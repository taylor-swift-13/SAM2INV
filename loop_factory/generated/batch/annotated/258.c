int main1(int k,int m){
  int l, u, v, t;

  l=42;
  u=l;
  v=m;
  t=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant l == 42;
  loop invariant k == \at(k, Pre);
  loop invariant 0 <= u;
  loop invariant u <= 42;
  loop invariant (u == 42) ==> (v == \at(m, Pre));

  loop assigns u, v;
*/
while (u>0) {
      v = v*3+5;
      u = u-1;
  }

}
