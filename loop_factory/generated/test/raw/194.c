int main1(){
  int l5eu, p8, dc2s, b9ya, fe;

  l5eu=48;
  p8=0;
  dc2s=1;
  b9ya=0;
  fe=p8;

  while (dc2s<=l5eu) {
      b9ya = b9ya+2*dc2s-1;
      dc2s++;
      fe += dc2s;
  }

  while (1) {
      if (!(fe<p8)) {
          break;
      }
      b9ya = b9ya + fe;
      fe += 1;
      dc2s = dc2s + fe;
  }

}
