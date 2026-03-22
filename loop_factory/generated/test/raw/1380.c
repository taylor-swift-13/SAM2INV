int main1(){
  int x, x5, qqx, p, duv, ej, u;

  x=(1%35)+15;
  x5=(1%35)+15;
  qqx=1;
  p=0;
  duv=0;
  ej=1;
  u=0;

  while (x!=x5) {
      if (x>x5) {
          x = x - x5;
          qqx -= p;
          duv = duv - ej;
      }
      else {
          x5 -= x;
          p -= qqx;
          ej = ej - duv;
      }
      u = u+ej-qqx;
  }

}
