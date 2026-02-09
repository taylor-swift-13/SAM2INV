
void foo(){
    int x = 1;
    int y = 0;
    
    while (y < 100000) {
        x = x + 4;
        y = y + 1;
    }

    /*@ assert x >= y; */
}