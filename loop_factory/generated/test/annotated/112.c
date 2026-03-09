int main1(){
  int vq, hb, v, c6nc, xu;
  vq=57;
  hb=vq;
  v=-1;
  c6nc=0;
  xu=hb;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (-1 <= v && v <= vq);
  loop invariant (0 <= c6nc && 0 <= xu && 0 <= hb && xu <= 2*vq);
  loop invariant c6nc % 3 == 0;
  loop invariant (hb > 0) ==> (c6nc == 0);
  loop invariant (hb > 0) ==> (xu == 57);
  loop assigns v, xu, c6nc, hb;
*/
while (hb>0) {
      if (!(!(v+1<=vq))) {
          v++;
      }
      else {
          v = vq;
      }
      xu = xu+v-v;
      c6nc = c6nc + 3;
      xu = xu + xu;
      hb = 0;
  }
}