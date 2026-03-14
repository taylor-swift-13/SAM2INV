int main1(){
  int ut, k, z6w, fzw;
  ut=1;
  k=0;
  z6w=k;
  fzw=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == z6w;
  loop invariant fzw + k == 8;
  loop invariant k <= ut;
  loop invariant ut == 1;
  loop assigns k, z6w, fzw;
*/
for (; k<=ut-1; k += 1) {
      z6w++;
      fzw -= 1;
  }
}