int main1(int a,int b,int m){
  int o, r, x, v, w;

  o=b+12;
  r=1;
  x=a;
  v=-6;
  w=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant o == b + 12;
  loop invariant x >= a;
  loop invariant (x - a) % 2 == 0;
  loop invariant 4*v == (x - a)*(x - a) + 2*(a - 1)*(x - a) - 24;
  loop invariant 4*v == x*x - 2*x - (a*a - 2*a + 24);
  loop invariant ((x - a) % 2 == 0);
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant ((x - a) % 2) == 0;
  loop invariant (4*v) == (x*x - 2*x + 2*a - a*a - 24);
  loop invariant v == -6 + ((x - a)/2) * a + ((x - a)/2) * (((x - a)/2) - 1);
  loop assigns x, v;
*/
while (1) {
      x = x+1;
      v = v+x;
      x = x+1;
      v = v-1;
  }

}
