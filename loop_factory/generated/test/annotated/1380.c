int main1(){
  int x, x5, qqx, p, duv, ej, u;
  x=(1%35)+15;
  x5=(1%35)+15;
  qqx=1;
  p=0;
  duv=0;
  ej=1;
  u=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x >= 0;
  loop invariant x5 >= 0;
  loop invariant x + x5 <= 32;
  loop invariant x % 16 == 0;
  loop invariant x5 % 16 == 0;
  loop invariant x*ej - x5*duv == 16;
  loop assigns x, x5, qqx, p, duv, ej, u;
*/
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