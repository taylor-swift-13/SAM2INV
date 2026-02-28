int main1(int a,int m,int q){
  int w, s, u, v, t;

  w=51;
  s=0;
  u=0;
  v=0;
  t=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= u <= w;
  loop invariant u % 3 == 0;
  loop invariant v % 3 == 0;
  loop invariant -u <= v <= u;
  loop invariant -3*(u/3) <= v <= 3*(u/3);
  loop invariant -3*u <= v;
  loop invariant v <= 3*u;
  loop invariant 0 <= u;
  loop invariant u <= w;
  loop invariant (u <= 27 ==> v == u) && (u > 27 ==> v == 54 - u) && w == 51;
  loop assigns u, v;
*/
while (u<w) {
      if (u<w/2) {
          v = v+3;
      }
      else {
          v = v-3;
      }
      u = u+1;
      u = u+2;
  }

}
