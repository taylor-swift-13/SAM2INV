int main1(){
  int kuy, jq2, y0c, oh;
  kuy=1+21;
  jq2=0;
  y0c=jq2;
  oh=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oh == y0c;
  loop invariant 0 <= jq2;
  loop invariant jq2 <= kuy;
  loop invariant 0 <= oh;
  loop invariant oh <= jq2;
  loop invariant kuy == 1 + 21;
  loop assigns jq2, oh, y0c;
*/
while (jq2 < kuy) {
      jq2 = jq2 + 1 + ((kuy - jq2) / (oh + 2));
      oh += 1;
      y0c++;
  }
}