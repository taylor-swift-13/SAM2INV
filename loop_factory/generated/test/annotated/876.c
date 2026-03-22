int main1(int l,int b){
  int k, fe, d6e, qrk;
  k=l*5;
  fe=k;
  d6e=k;
  qrk=b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fe - k == qrk - b;
  loop invariant fe >= k;
  loop assigns qrk, d6e, fe;
*/
while (fe-1>=0) {
      qrk++;
      d6e = qrk*qrk;
      fe += 1;
  }
}