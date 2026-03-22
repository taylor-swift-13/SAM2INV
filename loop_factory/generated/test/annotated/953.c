int main1(int e,int f){
  int or, l, gh, zk7;
  or=31;
  l=0;
  gh=1;
  zk7=or;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gh == l + 1;
  loop invariant zk7 == or;
  loop invariant (l == 0) ==> (e == \at(e,Pre));
  loop invariant (l > 0) ==> (e == l + zk7);
  loop invariant 0 <= l <= or;
  loop assigns f, gh, e, l;
*/
for (; l+1<=or; l = l + 1) {
      f = gh+zk7+e;
      gh = gh + 1;
      e = f-e;
  }
}