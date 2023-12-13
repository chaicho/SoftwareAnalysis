class Inter {
    public static void main(String[] args) {
        X x = new X();
        x.setF(123);
        int a = x.getF();
        Y y = new Y();
        y.setG(789);
        int b = y.getG();
    }

    static class X {
        int f;

        int getF() {
            return 123;
        }

        void setF(int f) {
            this.f = f;
        }
    }

    static class Y {
        int g;

        int getG() {
            return g;
        }

        void setG(int g) {
            this.g = g;
        }
    }
}
