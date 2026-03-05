int main1(){
  int uz, hd, v, sa3;
  uz=1+20;
  hd=uz;
  v=hd;
  sa3=uz;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= uz;
  loop invariant sa3 >= uz;
  loop invariant sa3 >= v;
  loop invariant hd == 21;
  loop invariant uz == 21;
  loop invariant sa3 == uz + (v - uz)*uz + ((v - uz)*(v - uz + 1))/2;
  loop assigns v, sa3;
*/
while (hd-2>=0) {
      if (hd<uz/2) {
          v = v + sa3;
      }
      else {
          v++;
      }
      sa3 += v;
  }
}