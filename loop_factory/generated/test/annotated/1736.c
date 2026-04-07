int main1(){
  int ikhq, k3g, i, dv;
  ikhq=1+25;
  k3g=1;
  i=1;
  dv=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (dv % 2) == 0;
  loop invariant dv <= ikhq;
  loop invariant ikhq == 26;
  loop invariant k3g == 1;
  loop invariant ((i == 1 && dv == 0) ||
                    (i == 2 && dv == 2) ||
                    (i == 4 && dv == 4) ||
                    (i == 8 && dv == 6) ||
                    (i == 16 && dv == 8) ||
                    (i == 32 && dv == 10));
  loop invariant dv >= 0;
  loop invariant i > 0;
  loop assigns i, dv;
*/
while (i<ikhq) {
      i = 2*i;
      dv += 1;
      dv = (k3g)+(dv);
  }
}