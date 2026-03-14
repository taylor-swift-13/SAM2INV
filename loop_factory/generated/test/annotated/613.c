int main1(int h){
  int eg2, bpa, vi;
  eg2=h;
  bpa=eg2;
  vi=h;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eg2 == h;
  loop invariant vi + bpa == 2 * h;
  loop invariant bpa <= h;
  loop assigns bpa, vi;
*/
for (; bpa>=1; bpa -= 1) {
      vi++;
  }
}