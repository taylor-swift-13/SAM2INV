int main1(int k,int p){
  int h, g, s;

  h=p-7;
  g=0;
  s=-6;

  while (g<=h-1) {
      if (g+5<=s+h) {
          s = s+1;
      }
      else {
          s = s+s;
      }
      g = g+1;
  }

}
