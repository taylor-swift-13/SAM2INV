int main1(){
  int pi, w, w0f, z, n8;
  pi=1-1;
  w=0;
  w0f=1;
  z=2;
  n8=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= w;
  loop invariant w <= pi;
  loop invariant n8 == (w + 3);
  loop invariant z == (2 + 3*w + (w*(w-1))/2);
  loop invariant w0f == 1 + (w*(w+1)*(w+5))/6;
  loop assigns w0f, z, n8, w;
*/
while (1) {
      if (!(w < pi)) {
          break;
      }
      w0f += z;
      z += n8;
      n8++;
      w += 1;
  }
}