int main1(){
  int k80, ne, w, bi7s;
  k80=36;
  ne=0;
  w=1;
  bi7s=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == 1 + 2*ne;
  loop invariant ne <= k80;
  loop invariant bi7s == 3 + 2*ne;
  loop invariant ne >= 0;
  loop invariant k80 == 36;
  loop assigns w, bi7s, ne;
*/
while (ne<k80) {
      w += 2;
      bi7s += 2;
      ne++;
  }
}