int main1(){
  int so, w74, dq;
  so=1;
  w74=so;
  dq=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant so == 1;
  loop invariant (dq == 0 || dq == so + 1);
  loop invariant w74 == 1;
  loop assigns dq;
*/
while (w74>=1) {
      dq = so-dq;
      dq = dq + 1;
  }
}