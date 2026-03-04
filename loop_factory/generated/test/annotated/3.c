int main1(int h,int t,int s){
  int jv3s, az, dw;
  jv3s=t+22;
  az=jv3s;
  dw=(t%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == \at(h, Pre) + ((\at(t, Pre) % 20) + 5 - dw) * az;
  loop invariant az == \at(t, Pre) + 22;
  loop invariant dw <= ((\at(t, Pre) % 20) + 5);
  loop invariant h == \at(h,Pre) + az * (((\at(t,Pre) % 20) + 5) - dw);
  loop invariant h - \at(h, Pre) == (((\at(t, Pre) % 20) + 5) - dw) * az;
  loop invariant az == jv3s;
  loop assigns dw, h, t, s;
*/
while (1) {
      if (!(dw>0)) {
          break;
      }
      dw--;
      h = h + az;
      t = t + s;
      s += h;
  }
}