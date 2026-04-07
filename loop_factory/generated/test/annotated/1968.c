int main1(){
  int w6k, cjz, al9;
  w6k=1;
  cjz=0;
  al9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2 * al9 == cjz;
  loop invariant cjz >= 0;
  loop invariant (cjz == 0 && w6k == 1) || w6k == (cjz - 1);
  loop invariant ( (cjz == 0 && w6k == 1 && al9 == 0)
                    || (cjz >= 1 && w6k == (cjz - 1)) );
  loop invariant w6k >= 1;
  loop invariant ((cjz == 0 && w6k == 1 && al9 == 0) || (cjz >= 1 && w6k == cjz - 1 && al9 == 1));
  loop assigns cjz, al9, w6k;
*/
while (1) {
      if (!(cjz++ < w6k)) {
          break;
      }
      al9 = (al9 + (cjz % 2) * 2)+(-(1));
      w6k = cjz++;
  }
}