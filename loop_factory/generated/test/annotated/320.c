int main1(int g,int p){
  int fz, dk, slm, x5wq, f;
  fz=g+8;
  dk=fz;
  slm=fz;
  x5wq=0;
  f=g;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fz == slm;
  loop invariant (dk == 0) || (dk == slm);
  loop invariant (dk == 0) ==> (x5wq == slm);
  loop invariant (dk != 0) ==> (x5wq == 0);
  loop invariant ((dk == slm && x5wq == 0 && slm == fz) ||
                    (dk == 0 && x5wq == slm && slm == fz));
  loop assigns x5wq, dk;
*/
while (1) {
      if (!(dk>0)) {
          break;
      }
      x5wq += slm;
      dk = 0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fz <= slm;
  loop invariant f == g * (fz - g - 7);
  loop assigns f, fz;
*/
while (fz<=slm-1) {
      f = f + g;
      fz += 1;
  }
}