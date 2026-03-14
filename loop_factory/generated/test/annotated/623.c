int main1(int l,int p){
  int qwgm, qvqu, j9v, g1z, c2;
  qwgm=l+9;
  qvqu=0;
  j9v=32;
  g1z=1;
  c2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c2 == qvqu;
  loop invariant qwgm == l + 9;
  loop invariant j9v >= 0;
  loop invariant qvqu == g1z - 1;
  loop assigns j9v, g1z, c2, qvqu;
*/
while (j9v>0&&g1z<=qwgm) {
      if (j9v>g1z) {
          j9v -= g1z;
      }
      else {
          j9v = 0;
      }
      g1z++;
      c2 += 1;
      qvqu += 1;
  }
}