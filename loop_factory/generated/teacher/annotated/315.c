int main1(int b,int m){
  int k, o, t;

  k=33;
  o=0;
  t=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 33;
  loop invariant o <= k;
  loop invariant 0 <= o;
  loop invariant t == -3 || t == 1;
  loop invariant m == \at(m, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant o >= 0;
  loop invariant o == 0 ==> t == -3;
  loop invariant 0 <= o <= k;
  loop invariant (o == 0) ==> (t == -3) && (o != 0) ==> (t == 1);
  loop assigns o, t;
*/
while (o<=k-1) {
      t = t-t;
      t = t+1;
      o = o+1;
  }

}
