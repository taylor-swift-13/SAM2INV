int main1(int a,int k){
  int m, u, v;

  m=20;
  u=m;
  v=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 20;
  loop invariant u == m;
  loop invariant u >= 2;
  loop invariant v >= -1;
  loop invariant k == \at(k, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant v == -1 || v >= u + 2;
  loop invariant u >= 3;
  loop assigns v;
*/
while (u>2) {
      v = v+3;
      v = v+u;
      if (u+7<=k+m) {
          v = v+v;
      }
  }

}
