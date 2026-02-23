int main1(int q){
  int h, u, v;

  h=58;
  u=0;
  v=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= u;
  loop invariant u <= h;
  loop invariant v == -5 + u*(u-1)/2;
  loop invariant h == 58;
  loop invariant q == \at(q, Pre);
  loop assigns u, v;
*/
while (u<=h-1) {
      v = v+u;
      u = u+1;
  }

}
