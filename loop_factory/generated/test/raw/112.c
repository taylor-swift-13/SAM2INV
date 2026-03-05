int main1(int a){
  int ym, b, hy, js8;

  ym=a;
  b=0;
  hy=0;
  js8=1;

  for (; hy>0&&js8<=ym; b += 1) {
      if (hy>js8) {
          hy = hy - js8;
      }
      else {
          hy = 0;
      }
      hy = hy + 1;
      js8++;
  }

}
