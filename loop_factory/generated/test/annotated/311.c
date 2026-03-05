int main1(int c){
  int kg, fv, u, e;
  kg=25;
  fv=0;
  u=-1;
  e=fv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kg == 25;
  loop invariant fv == 0;
  loop invariant c == \at(c, Pre);
  loop invariant e % (kg + 4) == fv % (kg + 4);
  loop invariant (fv < kg/2) ==> ((u + 1) % (kg + 4) == 0);
  loop invariant e >= 0;
  loop invariant u >= -1;
  loop assigns u, e;
*/
while (fv<=kg-1) {
      if (fv<kg/2) {
          u = u + e;
      }
      else {
          u = u + 1;
      }
      e += kg;
      e += 4;
  }
}