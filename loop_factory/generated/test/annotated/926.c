int main1(){
  int im, vp, c52l, w;
  im=1;
  vp=0;
  c52l=-2;
  w=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c52l == -2 + im * vp;
  loop invariant 0 <= vp;
  loop invariant vp <= im;
  loop invariant w <= vp;
  loop assigns c52l, vp, w;
*/
while (vp<im) {
      vp += 1;
      if (!(!(vp<=w))) {
          w = vp;
      }
      c52l += im;
  }
}