int main160(int t,int y,int x){
  int mnps, am, r8y, c4w;

  mnps=y-9;
  am=(y%40)+2;
  r8y=0;
  c4w=0;

  while (1) {
      if (!(am!=r8y)) {
          break;
      }
      r8y = am;
      am = (am+mnps/am)/2;
      c4w = c4w + 1;
      x = x + 3;
      t += 1;
      y = y+r8y-r8y;
  }

}
