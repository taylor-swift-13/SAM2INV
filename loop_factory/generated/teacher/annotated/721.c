int main1(int a,int m,int p,int q){
  int i, y, x, v, o, f, k, s;

  i=64;
  y=2;
  x=i;
  v=p;
  o=m;
  f=y;
  k=a;
  s=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == p + (x - 64) * 64 + ((x - 64) * (x - 63)) / 2;
  loop invariant x >= 64;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant 2*(v - p) == 2*(i+1)*(x - i) + (x - i)*(x - i - 1);
  loop invariant x >= i;
  loop invariant q == \at(q, Pre);
  loop invariant v == \at(p, Pre) + 64*(x - 64) + ((x - 64) * (x - 63)) / 2;
  loop invariant v == p + 65*(x - 64) + ((x - 64)*(x - 65))/2;
  loop invariant i == 64;
  loop invariant v == p + (x*(x+1))/2 - 2080;
  loop assigns x, v;
*/
while (1) {
      x = x+1;
      v = v+x;
  }

}
