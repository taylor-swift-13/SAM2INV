int main1(int m,int q){
  int n, u, v, f;

  n=61;
  u=0;
  v=m;
  f=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant f >= 0;

  loop invariant (f > 0) ==> (v == f*f);
  loop invariant (f == 0) ==> (v == m);
  loop invariant ((f == 0) ==> (v == m)) && ((f > 0) ==> (v == f*f));
  loop invariant n == 61;
  loop invariant f >= 0 && (((f == 0) && (v == m)) || (v == f*f));
  loop invariant m >= 0 ==> v >= 0;
  loop invariant v == m || v == f*f;
  loop invariant m == \at(m, Pre) && q == \at(q, Pre) && n == 61 && f >= 0 && (f == 0 ==> v == m);
  loop invariant f > 0 ==> v == f*f;
  loop invariant f == 0 ==> v == m;
  loop invariant m == \at(m, Pre) && q == \at(q, Pre) && (m == 0 ==> v == f*f);
  loop invariant (f != 0) ==> (v == f*f);
  loop assigns f, v;
*/
while (1) {
      f = f+1;
      v = f*f;
  }

}
