int main1(int k,int m){
  int b, e, v, u, i, l;

  b=23;
  e=1;
  v=-6;
  u=5;
  i=-4;
  l=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == -6;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant u <= 5;
  loop invariant b == 23;
  loop invariant (u - 5) % 6 == 0;
  loop assigns u;
*/
while (1) {
      u = u+v;
  }

}
