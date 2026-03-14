int main1(){
  int hrz, e, sam1, bsc, p6, kmwo;

  hrz=(1%14)+19;
  e=0;
  sam1=0;
  bsc=0;
  p6=(1%18)+5;
  kmwo=hrz;

  while (1) {
      if (!(p6>=1)) {
          break;
      }
      sam1 = sam1+1*1;
      e = e+1*1;
      p6 = (p6)+(-(1));
      bsc = bsc+1*1;
      kmwo += bsc;
  }

  while (1) {
      if (!(p6>sam1)) {
          break;
      }
      p6 -= sam1;
      sam1++;
      kmwo = kmwo + 3;
      bsc = bsc+(p6%9);
  }

}
