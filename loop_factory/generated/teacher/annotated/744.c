int main1(int a,int m,int p,int q){
  int v, d, x, c, h, r;

  v=20;
  d=0;
  x=a;
  c=1;
  h=p;
  r=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (x - a) % 5 == 0;
  loop invariant (h - p) % 4 == 0;
  loop invariant v == 20;
  loop invariant c - h + x == \at(a, Pre) - \at(p, Pre) + 1 || c - h + x == 5;
  loop invariant 4*x - 5*h == 4*a - 5*p;
  loop invariant x >= a;
  loop invariant h >= p;
  loop assigns c, x, h;
*/
while (1) {
      c = x;
      x = x+2;
      x = x+3;
      h = h+4;
      c = h-c;
  }

}
