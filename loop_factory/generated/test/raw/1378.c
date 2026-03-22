int main1(int o){
  int jkg3, s, w14;

  jkg3=(o%9)+20;
  s=jkg3+6;
  w14=o;

  while (1) {
      if (!(s>=jkg3+1)) {
          break;
      }
      w14 = w14*3;
      s = s - 3;
  }

}
