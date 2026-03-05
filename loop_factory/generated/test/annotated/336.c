int main1(){
  int hzh, q6k, c5k, h9;
  hzh=73;
  q6k=0;
  c5k=0;
  h9=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h9 == q6k + 1;
  loop invariant h9 <= hzh + 1;
  loop invariant c5k >= 0;
  loop invariant h9 >= 1;
  loop assigns c5k, h9, q6k;
*/
for (; c5k>0&&h9<=hzh; q6k++) {
      if (c5k>h9) {
          c5k = c5k - h9;
      }
      else {
          c5k = 0;
      }
      c5k++;
      h9 += 1;
  }
}