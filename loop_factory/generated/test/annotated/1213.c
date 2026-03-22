int main1(){
  int x9, ezw, p, i6, f, aex;
  x9=1+5;
  ezw=0;
  p=1;
  i6=6;
  f=0;
  aex=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i6 == 6 + 2*f;
  loop invariant p  == f*f + 5*f + 1;
  loop invariant aex == 4 + f*(f+1)/2;
  loop invariant ezw == f*(f-1)*(2*f-1)/6 + 5*f*(f-1)/2 + f;
  loop invariant f <= x9 + 1;
  loop invariant 0 <= f;
  loop invariant x9 == 6;
  loop assigns aex, ezw, p, i6, f;
*/
while (f<=x9) {
      f = f + 1;
      ezw += p;
      p = p + i6;
      i6 += 2;
      aex += f;
  }
}