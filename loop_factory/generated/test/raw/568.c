int main1(){
  int v4, mnh, g, j1;

  v4=196;
  mnh=0;
  g=0;
  j1=v4;

  while (g<=v4-1) {
      mnh = (mnh+1)%6;
      g++;
      j1 = j1 + mnh;
  }

}
