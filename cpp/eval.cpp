#include <iostream>
#include <map>
#include <memory>

class Value;
class Neutral;
class Term;
class NVar;
class NApp;

using namespace std;

class Value {
public:
    virtual ~Value() = default;
    virtual string to_string() const = 0;
    virtual shared_ptr<Value> apply(shared_ptr<Value> arg, int depth) = 0;
};

class Neutral : public Value {
public:
    virtual ~Neutral() = default;
};

class NApp : public Neutral {
    shared_ptr<Value> fun;
    shared_ptr<Value> arg;

public:
    NApp(shared_ptr<Value> f, shared_ptr<Value> a) : fun(f), arg(a) {}

    string to_string() const override {
        return "(" + fun->to_string() + " " + arg->to_string() + ")";
    }

    shared_ptr<Value> apply(shared_ptr<Value> arg, int depth) override {
        string indent(depth, ' ');
        cout << indent << "\033[1;34m⦇" << to_string() << "⦈\033[0m\n";
        return make_shared<NApp>(fun, arg);
    }
};

class NVar : public Neutral {
    string var;

public:
    NVar(const string &v) : var(v) {}

    string to_string() const override { return var; }

    shared_ptr<Value> apply(shared_ptr<Value> arg, int depth) override {
        return make_shared<NApp>(make_shared<NVar>(var), arg);
    }
};

class Environment {
    map<string, shared_ptr<Value>> bindings;

public:
    void bind(const string &name, shared_ptr<Value> value) {
        bindings[name] = value;
    }

    shared_ptr<Value> lookup(const string &name) const {
        auto it = bindings.find(name);
        if (it != bindings.end())
            return it->second;
        return make_shared<NVar>(name);
    }

    void print() const {
        cout << "[";
        auto itr = begin(bindings);
        while (itr != end(bindings)) {
            cout << itr->second->to_string() << "/" << itr->first;
            ++itr;
            if (itr != end(bindings))
                cout << ",";
        }
        cout << "]\n";
    }
};

class Term {
public:
    virtual ~Term() = default;
    virtual string to_string() const = 0;
    virtual shared_ptr<Value> eval(const shared_ptr<Environment> &env,
                                   int depth) const = 0;
};

class Closure : public Value {
    string var;
    shared_ptr<Term> body;
    shared_ptr<Environment> env;

public:
    Closure(const string &v, shared_ptr<Term> b, shared_ptr<Environment> e)
        : var(v), body(b), env(e) {}

    string to_string() const override {
        return "(λ" + var + "." + body->to_string() + ")";
    }

    shared_ptr<Value> apply(shared_ptr<Value> arg, int depth) override {
        auto new_env = make_shared<Environment>(*env);
        new_env->bind(var, arg);
        string indent(depth, ' ');
        cout << indent << "\033[1;32m⦇" << to_string() << " "
             << arg->to_string() << "⦈\033[0m\n";
        auto ret = body->eval(new_env, depth);
        cout << indent << "\033[1;31m" << ret->to_string() << "\033[0m\n";
        return ret;
    }
};

class Var : public Term {
    string name;

public:
    Var(const string &n) : name(n) {}

    string to_string() const override { return name; }

    shared_ptr<Value> eval(const shared_ptr<Environment> &env,
                           int depth) const override {
        string indent(depth, ' ');
        cout << indent << "\033[1;36m⦇" << name << "⦈\033[0m";
        env->print();
        cout << indent << env->lookup(name)->to_string() << "\n";
        return env->lookup(name);
    }
};

class App : public Term {
    shared_ptr<Term> fun;
    shared_ptr<Term> arg;

public:
    App(shared_ptr<Term> f, shared_ptr<Term> a) : fun(f), arg(a) {}

    string to_string() const override {
        return "(" + fun->to_string() + " " + arg->to_string() + ")";
    }

    shared_ptr<Value> eval(const shared_ptr<Environment> &env,
                           int depth) const override {
        string indent(depth, ' ');
        cout << indent << "\033[1;35m⦇" << to_string() << "⦈\033[0m";
        env->print();

        auto f = fun->eval(env, depth + 10);
        auto a = arg->eval(env, depth + 10);

        auto ret = f->apply(a, depth + 10);
        cout << indent << "\033[1;33m" << ret->to_string() << "\033[0m\n";
        return ret;
    }
};

class Abs : public Term {
    string var;
    shared_ptr<Term> body;

public:
    Abs(const string &v, shared_ptr<Term> b) : var(v), body(b) {}

    string to_string() const override {
        return "(λ" + var + "." + body->to_string() + ")";
    }

    shared_ptr<Value> eval(const shared_ptr<Environment> &env,
                           int depth) const override {
        string indent(depth, ' ');
        cout << indent << "\033[1;37m⦇λ" << var << "." << body->to_string()
             << "⦈\033[0m";
        env->print();
        return make_shared<Closure>(var, body, env);
    }
};

auto expr_0() -> void {
    auto z = make_shared<Var>("z");
    auto abs_z = make_shared<Abs>("z", z);

    auto y = make_shared<Var>("y");
    auto abs_y = make_shared<Abs>("y", y);

    auto x = make_shared<Var>("x");
    auto f = make_shared<Var>("f");
    auto fx = make_shared<App>(f, x);
    auto ff_x = make_shared<App>(f, fx);
    auto abs_x = make_shared<Abs>("x", ff_x);
    auto abs_f = make_shared<Abs>("f", abs_x);

    auto app_1 = make_shared<App>(abs_f, abs_y);
    auto full_term = make_shared<App>(app_1, abs_z);

    auto env = make_shared<Environment>();
    [[maybe_unused]] auto ret = full_term->eval(env, 0);
}

auto expr_1() -> void {
    auto z = make_shared<Var>("z");
    auto s_1 = make_shared<Var>("s");
    auto app_1 = make_shared<App>(s_1, z);
    auto app_2 = make_shared<App>(s_1, app_1);
    auto inner_abs = make_shared<Abs>("z", app_2);
    auto outer_abs = make_shared<Abs>("s", inner_abs);

    auto nested_abs = outer_abs;
    auto full_term = make_shared<App>(nested_abs, nested_abs);

    auto env = make_shared<Environment>();

    [[maybe_unused]] auto ret = full_term->eval(env, 0);
}

auto expr_2() -> void {
    auto z = make_shared<Var>("z");
    auto s_1 = make_shared<Var>("s");
    auto s_2 = make_shared<Var>("s");
    auto s_3 = make_shared<Var>("s");
    auto s_4 = make_shared<Var>("s");

    auto app_1 = make_shared<App>(s_4, z);
    auto app_2 = make_shared<App>(s_3, app_1);
    auto app_3 = make_shared<App>(s_2, app_2);
    auto app_4 = make_shared<App>(s_1, app_3);

    auto abs_2 = make_shared<Abs>("z", app_4);
    auto abs_1 = make_shared<Abs>("s", abs_2);

    auto f = make_shared<Var>("f");
    auto x = make_shared<Var>("x");

    auto full_term = make_shared<App>(make_shared<App>(abs_1, f), x);

    auto env = make_shared<Environment>();

    [[maybe_unused]] auto ret = full_term->eval(env, 0);
}

auto expr_3() -> void {
    auto z = make_shared<Var>("z");
    auto s_1 = make_shared<Var>("s");
    auto app_1 = make_shared<App>(s_1, z);
    auto app_2 = make_shared<App>(s_1, app_1);
    auto inner_abs = make_shared<Abs>("z", app_2);
    auto outer_abs = make_shared<Abs>("s", inner_abs);

    auto nested_abs = outer_abs;
    auto f = make_shared<Var>("f");
    auto x = make_shared<Var>("x");

    auto first_app = make_shared<App>(nested_abs, nested_abs);
    auto second_app = make_shared<App>(first_app, f);
    auto full_term = make_shared<App>(second_app, x);

    auto env = make_shared<Environment>();

    [[maybe_unused]] auto ret = full_term->eval(env, 0);
}

auto main() -> int { expr_3(); }