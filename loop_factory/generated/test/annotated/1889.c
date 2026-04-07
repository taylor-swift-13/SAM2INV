int main1(){
  int h, zh, g7, t80, fz, o3, jv0x, y8;
  h=1;
  zh=0;
  g7=zh;
  t80=zh;
  fz=zh;
  o3=h;
  jv0x=h;
  y8=zh;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g7 == 0;
  loop invariant t80 == 0;
  loop invariant fz == 2*zh;
  loop invariant y8 == zh*(zh+1)/2;
  loop invariant o3 == 1 + zh;
  loop invariant jv0x >= 1;
  loop invariant o3 == zh + h;
  loop invariant 0 <= zh <= h;
  loop assigns fz, g7, zh, t80, y8, jv0x, o3;
*/
while (zh < h) {
      if (!(!((g7 == 0)))) {
          fz += 2;
          g7 = 0;
          zh++;
      }
      else {
          t80++;
          zh++;
      }
      if (zh+5<=o3+h) {
          y8 += jv0x;
      }
      jv0x += fz;
      o3 += g7;
      o3 = o3 + 1;
      jv0x += o3;
      if ((zh%6)==0) {
          jv0x += o3;
      }
      y8 += zh;
  }
}