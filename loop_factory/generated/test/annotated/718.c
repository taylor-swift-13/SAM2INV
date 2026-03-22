int main1(int y,int i){
  int gst, r3q, p, z7;
  gst=(y%26)+11;
  r3q=(y%40)+2;
  p=0;
  z7=i;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z7 == i + (r3q - ((\at(y,Pre) % 40) + 2));
  loop assigns p, r3q, z7;
*/
while (1) {
      if (!(r3q!=p)) {
          break;
      }
      p = r3q;
      r3q = (r3q+gst/r3q)/2;
      z7 = z7+r3q-p;
  }
}