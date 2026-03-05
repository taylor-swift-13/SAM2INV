int main102(int f){
  int xp, lv0, a;

  xp=(f%39)+7;
  lv0=xp;
  a=2;

  while (1) {
      if (!(lv0>1)) {
          break;
      }
      if (a==1) {
          a = 2;
      }
      else {
          if (a==2) {
              a = 1;
          }
      }
      f = f + a;
  }

}
