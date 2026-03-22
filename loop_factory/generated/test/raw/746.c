int main1(){
  int h, gzk, dom, b, l1;

  h=(1%60)+60;
  gzk=(1%9)+2;
  dom=0;
  b=0;
  l1=12;

  while (h>gzk*dom+b) {
      if (!(!(b==gzk-1))) {
          b += 1;
      }
      else {
          b = 0;
          dom += 1;
      }
      l1 = l1+dom-b;
  }

}
