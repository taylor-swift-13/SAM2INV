int main1(){
  int he2, yi, xpf5, awt;
  he2=48;
  yi=0;
  xpf5=0;
  awt=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= awt;
  loop invariant 0 <= yi <= he2;
  loop invariant awt == 8 - yi;
  loop invariant xpf5 == (23*yi - yi*yi)/2;
  loop assigns xpf5, yi, awt;
*/
while (yi<he2&&awt>0) {
      xpf5 += awt;
      yi++;
      xpf5 = xpf5 + 3;
      awt = awt - 1;
  }
}