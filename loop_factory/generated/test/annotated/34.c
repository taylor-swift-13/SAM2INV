int main1(int e,int u){
  int j, wb;
  j=0;
  wb=j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 0;
  loop invariant wb == 0;
  loop invariant u == \at(u, Pre);
  loop invariant e >= \at(e, Pre);
  loop invariant (e - \at(e, Pre)) % 3 == 0;
  loop assigns e, wb;
*/
while (wb!=0&&wb!=0) {
      if (wb>wb) {
          wb = wb - wb;
      }
      else {
          wb = wb - wb;
      }
      e += j;
      e = e + 3;
  }
}