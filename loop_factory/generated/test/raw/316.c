int main1(int t){
  int gh, x41, ma2;

  gh=t*3;
  x41=gh;
  ma2=0;

  while (x41<gh) {
      ma2++;
      if (ma2>=7) {
          ma2 = ma2 - 7;
          ma2++;
      }
      x41 += 1;
  }

}
