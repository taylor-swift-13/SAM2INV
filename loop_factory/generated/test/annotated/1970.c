int main1(int d){
  int fe, f0, nr5, w;
  fe=38;
  f0=0;
  nr5=f0;
  w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (f0 >= fe) ==> (nr5 == \at(d, Pre));
  loop invariant 0 <= f0 <= fe;
  loop invariant fe == 38;
  loop invariant nr5 == d * (f0 / fe);
  loop invariant ((f0 < fe) ==> (nr5 == 0 && w == 0)) && ((f0 >= fe) ==> (nr5 == d && w == d));
  loop assigns f0, w, nr5;
*/
while (f0 < fe) {
      f0 = f0 + 1;
      w = w + d * (f0 >= fe);
      nr5 = nr5 + d * (f0 >= fe);
  }
}