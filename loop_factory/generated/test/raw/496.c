int main1(){
  int li, n, l9h, gb, i4, ese, l3;

  li=1*3;
  n=li;
  l9h=0;
  gb=0;
  i4=0;
  ese=(1%18)+5;
  l3=3;

  while (ese>=1) {
      gb = gb+1*1;
      ese = ese - 1;
      l9h = l9h+1*1;
      i4 = i4+1*1;
      l3 = l3*2+(gb%7)+0;
  }

  while (n>l9h) {
      n = n - l9h;
      li += n;
      l9h += 1;
      li = li*2;
  }

}
