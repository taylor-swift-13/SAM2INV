int main1(int m,int o){
  int e, k7, krk, ss;

  e=o;
  k7=0;
  krk=3;
  ss=0;

  for (; k7<e; k7 = k7 + 1) {
      ss = k7%5;
      if (k7>=krk) {
          krk = (k7-krk)%5;
          krk = krk+ss-krk;
      }
      else {
          krk += ss;
      }
      o += ss;
  }

}
