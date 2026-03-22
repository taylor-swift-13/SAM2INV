int main1(int j,int h){
  int tu, o, gq5c, nay;
  tu=j+21;
  o=tu;
  gq5c=j;
  nay=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nay + gq5c * o == j * tu;
  loop invariant nay == j * (tu - o);
  loop assigns nay, gq5c, o;
*/
while (o>0) {
      nay = nay+gq5c*o;
      gq5c = gq5c + tu;
      gq5c = gq5c+j+h;
      o = 0;
  }
}