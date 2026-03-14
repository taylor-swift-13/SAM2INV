int main1(int n,int e){
  int jv, qxsh, em, you, dtw;
  jv=n-4;
  qxsh=0;
  em=0;
  you=3;
  dtw=jv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant you == 3 - qxsh;
  loop invariant dtw == jv * (qxsh + 1);
  loop invariant qxsh >= 0;
  loop invariant em == 3*qxsh - qxsh*(qxsh - 1)/2;
  loop invariant qxsh <= 3;
  loop assigns qxsh, em, you, dtw;
*/
while (1) {
      if (!(qxsh<jv&&you>0)) {
          break;
      }
      qxsh += 1;
      em = em + you;
      you -= 1;
      dtw += jv;
  }
}