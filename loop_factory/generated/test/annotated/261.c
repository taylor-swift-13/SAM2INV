int main1(int e,int q){
  int gc, okr1, atn;
  gc=e;
  okr1=gc;
  atn=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant okr1 == \at(e, Pre);
  loop invariant gc == \at(e, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant atn == 0 || atn == gc + 1;
  loop invariant okr1 != 0 ==> (e - \at(e, Pre)) % okr1 == 0;
  loop invariant e >= \at(e, Pre);
  loop assigns atn, e;
*/
while (okr1-4>=0) {
      atn = gc-atn;
      atn += 1;
      e = e + okr1;
  }
}