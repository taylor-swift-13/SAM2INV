int main1(int c){
  int lt7, rym, f, r, tt, z6aa, b;

  lt7=171;
  rym=0;
  f=rym;
  r=lt7;
  tt=0;
  z6aa=lt7;
  b=0;

  while (1) {
      r = r + 1;
      f = f+r*r;
      z6aa = z6aa+(f%7);
      b = b+(r%9);
      c = c*3+(r%7)+1;
      c = c*c+tt;
      rym += 1;
      if (rym>=lt7) {
          break;
      }
  }

}
