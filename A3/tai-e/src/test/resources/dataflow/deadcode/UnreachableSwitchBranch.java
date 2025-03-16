class UnreachableSwitchBranch {

    void lookupSwitch() {
        int x = 1;
        int y = x << 3;
        switch (x + y - 1) {
            case 2:
                use(2);
                break;  // unreachable case
            case 4:
                use(4);
                break; // unreachable case
            case 8:
                while (x == 1) {
                    x = 1;
                }
                break;
            default:
                use(8);
                break; // unreachable case
        }
    }

    int unreachableSwitchBranch() {
        int x = 2, y;
        switch (x) {
            case 1: y = 100; break; // unreachable branch
            case 2: y = 200;
            case 3: y = 300; break; // fall through
            default: y = 666; // unreachable branch
        }
        return y;
    }

    void use(int x) {
    }
}
