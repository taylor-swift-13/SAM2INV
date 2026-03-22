int main1(int b){
  int kz, jyt, n2, mh;
  kz=42;
  jyt=0;
  n2=kz;
  mh=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mh == 1 + jyt*kz - (jyt*(jyt+1))/2;
  loop invariant b == \at(b, Pre) + jyt;
  loop invariant n2 == kz - jyt;
  loop invariant 0 <= jyt <= kz;
  loop assigns jyt, n2, mh, b;
*/
while (1) {
      if (!(jyt<kz&&n2>0)) {
          break;
      }
      jyt = (1)+(jyt);
      n2 -= 1;
      mh += n2;
      b += 1;
  }
}