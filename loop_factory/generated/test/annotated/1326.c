int main1(int t,int b){
  int tbpu, w5h5, gjt, ou;
  tbpu=t-4;
  w5h5=0;
  gjt=1;
  ou=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ou == 1 + 2*w5h5;
  loop invariant gjt == (w5h5 + 1) * (w5h5 + 1);
  loop invariant w5h5 >= 0;
  loop assigns w5h5, ou, gjt, t;
*/
while (gjt<=tbpu) {
      w5h5 += 1;
      ou += 2;
      gjt += ou;
      t = t+(gjt%2);
  }
}