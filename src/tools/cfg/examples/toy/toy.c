

int main(int x, char** y)
{
  int i = 0;


  if (x < -200)
  {
    i *= 10;
  } else {
    i *= 20;
  }

  while (x > 0)
  {
    x-= 3;

    if (x & 0xF)
    {
      i++;
    } else {
      i--;
    }
  }

  if (x < 0)
  {
    i *= 5;
  } else {
    i *= 3;
  }
  

  return i;
}
