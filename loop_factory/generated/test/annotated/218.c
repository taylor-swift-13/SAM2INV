int main1(){
  int nzg, evzs;
  nzg=34;
  evzs=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant evzs <= nzg;
  loop invariant evzs >= 0;
  loop invariant evzs % 2 == 0;
  loop invariant nzg == 34;
  loop assigns evzs;
*/
while (evzs<nzg) {
      evzs += 2;
  }
}