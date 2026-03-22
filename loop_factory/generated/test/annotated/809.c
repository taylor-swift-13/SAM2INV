int main1(){
  int m9, j3s, e, dtw;
  m9=1-9;
  j3s=1;
  e=-5;
  dtw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (((j3s == 1) ==> (dtw == 0)) && ((j3s == m9) ==> (dtw == e)));
  loop invariant j3s == 1 || j3s == m9;
  loop invariant dtw <= 0;
  loop assigns dtw, j3s;
*/
while (j3s<=m9-1) {
      dtw = dtw+e*j3s;
      j3s = m9;
  }
}