int main1(int k,int e){
  int ifbs, h7r, j, z6z, nm;
  ifbs=55;
  h7r=1;
  j=ifbs;
  z6z=0;
  nm=h7r;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z6z == 0;
  loop invariant nm == 1;
  loop invariant h7r >= 1;
  loop invariant j >= 55;
  loop invariant e == \at(e, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant j == ifbs + (h7r - 1) / 2;
  loop assigns z6z, j, nm, h7r;
*/
while (h7r<=ifbs/3) {
      z6z = z6z*z6z;
      j = j + h7r;
      nm = nm+j*z6z;
      h7r = h7r*3;
  }
}